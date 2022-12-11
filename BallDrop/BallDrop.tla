---- MODULE BallDrop ---------------------------------------------------------
VARIABLES placement
vars == <<placement>>

TypeOK == placement \in {"floor", "table", "freefall", "under couch"}

Init ==
  /\ placement = "floor"

Lift ==
  /\ placement = "floor"
  /\ placement' = "table"

RollOnTable ==
  /\ placement = "table"
  /\ placement' = "freefall"

RollOnFloor ==
  /\ placement = "floor"
  /\ placement' = "under couch"

Fall ==
  /\ placement = "freefall"
  /\ placement' = "floor"

Next ==
  \/ Lift
  \/ RollOnFloor
  \/ RollOnTable
  \/ Fall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_placement(Fall)

--------------------------------------------------------------------------------
GravityWorks == (placement = "freefall") ~> (placement = "floor")
UnderCouchIsLostForever == []((placement = "under couch") => [](placement = "under couch"))
================================================================================
