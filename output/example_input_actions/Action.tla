----MODULE Action ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals


Action == 
  /\ IF a = 1 THEN a' = 2
====
