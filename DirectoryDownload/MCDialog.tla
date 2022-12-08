---- MODULE MCDialog -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANTS
   NumFiles                 \* Needed for Messages
   , MaxFileSize            \* Needed for Messages
   , MaxConcurrentTransfers \* Needed for Messages

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
