---- MODULE MCDialog -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   dialog_state
   , chan_local_to_dialog

vars == <<dialog_state, chan_local_to_dialog>>

Dialog == INSTANCE Dialog

Init == Dialog!Init

Next ==
   \/ Dialog!Open
   \/ Dialog!Accept
   \/ Dialog!Close
   \/ Dialog!Request

Spec == Init /\ [][Next]_vars

================================================================================
