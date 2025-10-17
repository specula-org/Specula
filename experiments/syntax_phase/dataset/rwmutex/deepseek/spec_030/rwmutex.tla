---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
VARIABLES writer, upgradeable, beingUpgraded, readers, waiting
vars == <<writer, upgradeable, beingUpgraded, readers, waiting>>
Init == 
    writer = FALSE /\
    upgradeable = FALSE /\
    beingUpgraded = FALSE /\
    readers = 0 /\
    waiting = << >>
TypeOK == 
    writer \in BOOLEAN /\
    upgradeable \in BOOLEAN /\
    beingUpgraded \in BOOLEAN /\
    readers \in Nat /\
    waiting \in Seq({"read", "write", "upread"})
TryRead == 
    \/ /\ ~writer /\ ~beingUpgraded
       /\ readers' = readers + 1
       /\ UNCHANGED << writer, upgradeable, beingUpgraded, waiting >>
    \/ /\ (writer \/ beingUpgraded)
       /\ waiting' = Append(waiting, "read")
       /\ UNCHANGED << writer, upgradeable, beingUpgraded, readers >>
TryWrite == 
    \/ /\ ~writer /\ ~upgradeable /\ readers = 0 /\ ~beingUpgraded
       /\ writer' = TRUE
       /\ UNCHANGED << upgradeable, beingUpgraded, readers, waiting >>
    \/ /\ (writer \/ upgradeable \/ readers > 0 \/ beingUpgraded)
       /\ waiting' = Append(waiting, "write")
       /\ UNCHANGED << writer, upgradeable, beingUpgraded, readers >>
TryUpread == 
    \/ /\ ~writer /\ ~upgradeable
       /\ upgradeable' = TRUE
       /\ UNCHANGED << writer, beingUpgraded, readers, waiting >>
    \/ /\ (writer \/ upgradeable)
       /\ waiting' = Append(waiting, "upread")
       /\ UNCHANGED << writer, upgradeable, beingUpgraded, readers >>
ReleaseRead == 
    /\ readers > 0
    /\ LET new_readers = readers - 1 IN
    \/ /\ new_readers > 0
          /\ readers' = new_readers
          /\ UNCHANGED << writer, upgradeable, beingUpgraded, waiting >>
       \/ /\ new_readers = 0
          /\ \/ /\ waiting = << >>
                /\ readers' = 0
                /\ UNCHANGED << writer, upgradeable, beingUpgraded, waiting >>
             \/ /\ waiting # << >>
                /\ LET first == Head(waiting) IN
                   \/ /\ first = "read" /\ ~writer /\ ~beingUpgraded
                         /\ readers' = 1
                         /\ waiting' = Tail(waiting)
                         /\ UNCHANGED << writer, upgradeable, beingUpgraded >>
                      \/ /\ first = "write" /\ ~writer /\ ~upgradeable /\ new_readers = 0 /\ ~beingUpgraded
                         /\ writer' = TRUE
                         /\ readers' = 0
                         /\ waiting' = Tail(waiting)
                         /\ UNCHANGED << upgradeable, beingUpgraded >>
                      \/ /\ first = "upread" /\ ~writer /\ ~upgradeable
                         /\ upgradeable' = TRUE
                         /\ readers' = 0
                         /\ waiting' = Tail(waiting)
                         /\ UNCHANGED << writer, beingUpgraded >>
                      \/ /\ waiting' = Append(Tail(waiting), first)
                         /\ readers' = 0
                         /\ UNCHANGED << writer, upgradeable, beingUpgraded >>
ReleaseWrite == 
    /\ writer = TRUE
    /\ \/ /\ waiting = << >>
          /\ writer' = FALSE
          /\ UNCHANGED << upgradeable, beingUpgraded, readers, waiting >>
       \/ /\ waiting # << >>
          /\ LET first == Head(waiting) IN
             \/ /\ first = "read" /\ ~beingUpgraded
                   /\ readers' = readers + 1
                   /\ writer' = FALSE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << upgradeable, beingUpgraded >>
                \/ /\ first = "write" /\ ~upgradeable /\ readers = 0 /\ ~beingUpgraded
                   /\ writer' = TRUE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << upgradeable, beingUpgraded, readers >>
                \/ /\ first = "upread" /\ ~upgradeable
                   /\ upgradeable' = TRUE
                   /\ writer' = FALSE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << beingUpgraded, readers >>
                \/ /\ waiting' = Append(Tail(waiting), first)
                   /\ writer' = FALSE
                   /\ UNCHANGED << upgradeable, beingUpgraded, readers >>
ReleaseUpread == 
    /\ upgradeable = TRUE
    /\ \/ /\ waiting = << >>
          /\ upgradeable' = FALSE
          /\ UNCHANGED << writer, beingUpgraded, readers, waiting >>
       \/ /\ waiting # << >>
          /\ LET first == Head(waiting) IN
             \/ /\ first = "read" /\ ~writer /\ ~beingUpgraded
                   /\ readers' = readers + 1
                   /\ upgradeable' = FALSE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << writer, beingUpgraded >>
                \/ /\ first = "write" /\ ~upgradeable /\ readers = 0 /\ ~beingUpgraded
                   /\ writer' = TRUE
                   /\ upgradeable' = FALSE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << beingUpgraded, readers >>
                \/ /\ first = "upread" /\ ~upgradeable
                   /\ upgradeable' = TRUE
                   /\ waiting' = Tail(waiting)
                   /\ UNCHANGED << writer, beingUpgraded, readers >>
                \/ /\ waiting' = Append(Tail(waiting), first)
                   /\ upgradeable' = FALSE
                   /\ UNCHANGED << writer, beingUpgraded, readers >>
StartUpgrade == 
    /\ upgradeable = TRUE
    /\ ~beingUpgraded
    /\ beingUpgraded' = TRUE
    /\ UNCHANGED << writer, readers, waiting >>
CompleteUpgrade == 
    /\ upgradeable = TRUE
    /\ beingUpgraded = TRUE
    /\ readers = 0
    /\ writer' = TRUE
    /\ beingUpgraded' = FALSE
    /\ UNCHANGED << readers, waiting >>
Downgrade == 
    /\ writer = TRUE
    /\ writer' = FALSE
    /\ upgradeable' = TRUE
    /\ UNCHANGED << beingUpgraded, readers, waiting >>
Next == 
    TryRead \/ TryWrite \/ TryUpread \/ 
    ReleaseRead \/ ReleaseWrite \/ ReleaseUpread \/ 
    StartUpgrade \/ CompleteUpgrade \/ Downgrade
Spec == 
    Init /\ 
    [][Next]_vars /\ 
    WF_vars(Next)
====