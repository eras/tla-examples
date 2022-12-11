---- MODULE MCDialog -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   dialog_state
   , chan_local_to_dialog

vars == <<dialog_state, chan_local_to_dialog>>

LOCAL INSTANCE DialogChannel
Dialog == INSTANCE Dialog

Init ==
   /\ Dialog!Init
   /\ LocalToDialog!Init

Next ==
   \/ Dialog!Open
   \/ Dialog!Accept
   \/ Dialog!Close
   \/ Dialog!Request

Spec == Init /\ [][Next]_vars

================================================================================
