---- MODULE Channels -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANTS
   NumFiles                 \* Needed for Messages
   , NumFileNames           \* Needed for Messages
   , MaxFileSize            \* Needed for Messages
   , MaxConcurrentTransfers \* Needed for Messages

VARIABLES
   chan_local_to_remote      (* Channel from local to remote *)
 , chan_remote_to_local      (* Channel from remote to local *)

LOCAL INSTANCE Messages

chans == <<chan_local_to_remote, chan_remote_to_local>>

LocalToRemote == INSTANCE Channel WITH channel <- chan_local_to_remote, Data <- MsgLocalToRemote
RemoteToLocal == INSTANCE Channel WITH channel <- chan_remote_to_local, Data <- MsgRemoteToLocal

UnchangedVarsChannels ==
   /\ LocalToRemote!UnchangedVars
   /\ RemoteToLocal!UnchangedVars

InitChannels ==
   /\ LocalToRemote!Init
   /\ RemoteToLocal!Init

================================================================================
