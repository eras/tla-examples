---- MODULE LocalDialogChannels ------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES
   chan_local_to_dialog      (* Channel from local to dialog *)

LOCAL INSTANCE LocalDialogMessages

INSTANCE DialogChannel          (* LocalToDialog *)

chans == <<chan_local_to_dialog>>

(* These are named in a way that they don't conflict other operators, so this module can
 * be INSTANCEd directly to other modules.. But really for consistency with LocalRemoteChannels
 * which actually uses that. *)

UnchangedVarsChannels == UNCHANGED<<chans>>

(* Are all the channels empty? *)
QuiescentChannels ==
   /\ ~LocalToDialog!Busy

UnchangedChannels ==
   /\ LocalToDialog!UnchangedVars

InitChannels ==
   /\ LocalToDialog!Init

================================================================================
