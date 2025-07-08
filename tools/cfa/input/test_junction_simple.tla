---- MODULE test_junction_simple ----
VARIABLES x, y, z

SimpleAction == 
    /\ x = 1
    /\ y = 2
    /\ z = 3

DisjunctionAction == 
    \/ x = 1
    \/ y = 2
    \/ z = 3

NestedAction == 
    /\ x = 1
    /\ y = 2
        \/ option1
        \/ option2
    /\ z = 3

====