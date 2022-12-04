---- MODULE Main ---------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Json             (* ToJson *)
LOCAL INSTANCE TLC

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers
   , MaxSendQueue

VARIABLES
   remote_files                 (* The files the remote has *)
   , remote_state               (* Remote state *)
   , remote_send_queue          (* Blocks pending send *)
   , local_files                (* The files the local knows of *)
   , local_state                (* State of the local scanner/transfer system *)
   , local_transfers            (* On-going transfers *)
   , chan_local_to_remote       (* Channel from local to remote *)
   , chan_remote_to_local       (* Channel from remote to local *)

LOCAL INSTANCE Records
LOCAL INSTANCE Util             (* Image *)

Channels == INSTANCE Channels

Local == INSTANCE Local
Remote == INSTANCE Remote

vars == <<remote_files, remote_state, remote_send_queue,
          local_files, local_state, local_transfers,
          chan_local_to_remote, chan_remote_to_local>>

TypeOK ==
   /\ Assert(Local!TypeOK, "Local!TypeOK")
   /\ Assert(Remote!TypeOK, "Remote!TypeOK")

Init ==
   /\ Remote!Init
   /\ Local!Init
   /\ Channels!InitChannels

LocalNext ==
   /\ Local!Next
   /\ Remote!UnchangedVars

RemoteNext ==
   /\ Remote!Next
   /\ Local!UnchangedVars

AllFilesAreTransferred ==
   /\ \A remote_file \in Image(remote_files):
      \E file_id \in Local!HasFileId:
         /\ local_files[file_id].remote_file = remote_file
         /\ local_files[file_id].state = "transferred"
   /\ \A transfer_id \in TransferId:
      local_transfers[transfer_id] = <<>>

AllFileAreTransferredAction ==
   /\ AllFilesAreTransferred
   /\ Local!UnchangedVars
   /\ Remote!UnchangedVars
   /\ Channels!UnchangedVarsChannels

Next ==
   \/ LocalNext
   \/ RemoteNext
   (* \/ AllFileAreTransferredAction     (\* stutter on finish *\) *)

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ WF_vars(Next)

EventuallyAllFilesAreTransferred ==
   Init => <> AllFilesAreTransferred

AllMessages ==
   UNION({{{<<"local", 1>>} \X {<<"remote", 1>>} \X Channels!LocalToRemote!Sending}
        , {{<<"remote", 1>>} \X {<<"local", 1>>} \X Channels!RemoteToLocal!Sending}})

State ==
   [ local |-> <<>>,
     remote |-> <<>> ]

AliasMessages ==
   [lane_order_json |-> ToJson(<<"local", "remote">>),
    messages_json   |-> ToJson(AllMessages),
    state_json      |-> ToJson(State) ]

================================================================================
