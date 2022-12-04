---- MODULE Main ---------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Json             (* ToJson *)
LOCAL INSTANCE TLC

CONSTANTS
   NumFiles
   , MaxFileSize
   , MaxConcurrentTransfers
   , MaxSendQueue
   , ForceStateTraces

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

(* Does the local file state match the remote file state? *)
AllFilesAreTransferred ==
   /\ \A remote_file \in Image(remote_files):
      \E file_id \in Local!HasFileId:
         /\ local_files[file_id].remote_file = remote_file
         /\ local_files[file_id].state = "transferred"
   /\ \A transfer_id \in TransferId:
      local_transfers[transfer_id] = <<>>

(* Is everything transferred and queues empty? *)
Finished ==
   /\ AllFilesAreTransferred
   /\ Channels!QuiescentChannels
   /\ Remote!Quiescent
   /\ UNCHANGED<<vars>>
   /\ Assert(~ForceStateTraces, "Force state trace")

Next ==
   \/ LocalNext
   \/ RemoteNext
   \/ Finished                  (* stutter on finish, instead of deadlock *)

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ WF_<<local_transfers, remote_send_queue, chan_remote_to_local, chan_local_to_remote>>(Next)

(* After starting the system, at some point we end up having all files transferred *)
EventuallyAllFilesAreTransferred ==
   Init => <> AllFilesAreTransferred

(* Messages currently in the flight, for the benefit of tlsd *)
AllMessages ==
   UNION({{{<<"local", 1>>} \X {<<"remote", 1>>} \X Channels!LocalToRemote!Sending}
        , {{<<"remote", 1>>} \X {<<"local", 1>>} \X Channels!RemoteToLocal!Sending}})

(* An expression of some state, to display in the TLSD output *)
State ==
   [ local |-> <<Local!State>>,
     remote |-> <<Remote!State>> ]

(* TLSD output mapping *)
AliasMessages ==
   [lane_order_json |-> ToJson(<<"local", "remote">>),
    messages_json   |-> ToJson(AllMessages),
    state_json      |-> ToJson(State) ]

================================================================================
