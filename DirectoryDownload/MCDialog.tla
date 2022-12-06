---- MODULE MCDialog -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   dialog_state
   , dialog_request

vars == <<dialog_state, dialog_request>>

Dialog == INSTANCE Dialog

Init == Dialog!Init

Next ==
   \/ Dialog!Open
   \/ Dialog!Accept
   \/ Dialog!Close
   \/ Dialog!Request

Spec == Init /\ [][Next]_vars

================================================================================
