---- MODULE Main ---------------------------------------------------------------
(* The model that ties everything together:
   Local is the process that attempts to communicate with a Remote to transfer files
   Remote is the remote service that responds to those queries
   Dialog is a dialog that can be shown to user once the transfer is complete

   and then there are channels used for communication and reducing coupling:
   LocalRemoteChannels (two chanels) and LocalDialogChannels (one channel)
*)
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
   , dialog_state               (* State of the dialog *)
   , chan_local_to_dialog       (* Channel to request dialogs *)

LOCAL INSTANCE LocalRemoteTypes
LOCAL INSTANCE Util             (* Image *)

LocalRemoteChannels == INSTANCE LocalRemoteChannels
LocalDialogChannels == INSTANCE LocalDialogChannels

Dialog == INSTANCE Dialog
Local == INSTANCE Local
Remote == INSTANCE Remote

vars == <<remote_files, remote_state, remote_send_queue,
          local_files, local_state, local_transfers,
          chan_local_to_remote, chan_remote_to_local,
          chan_local_to_dialog, dialog_state>>

TypeOK ==
   /\ Assert(Local!TypeOK, "Local!TypeOK")
   /\ Assert(Remote!TypeOK, "Remote!TypeOK")

Init ==
   /\ Dialog!Init
   /\ Remote!Init
   /\ Local!Init
   /\ LocalRemoteChannels!InitChannels
   /\ LocalDialogChannels!InitChannels

LocalNext ==
   /\ Local!Next
   /\ Remote!UnchangedVars

RemoteNext ==
   /\ Remote!Next
   /\ Local!UnchangedVars
   /\ Dialog!UnchangedVars

DialogNext ==
   /\ Dialog!Next
   /\ Local!UnchangedVars
   /\ Remote!UnchangedVars
   /\ LocalRemoteChannels!UnchangedVarsChannels

(* Does the local file state match the remote file state? *)
AllLocalFilesAreTransferredAsInRemote ==
   /\ \A remote_file \in Image(remote_files):
      \E file_id \in Local!HasFileId:
         /\ local_files[file_id].remote_file = remote_file
         /\ local_files[file_id].state = "transferred"

AllLocalFileInTransferredState == (\A file_id \in Local!HasFileId: local_files[file_id].state = "transferred")

NoTransfers ==
   /\ \A transfer_id \in TransferId:
      local_transfers[transfer_id] = <<>>

OnceTransferredAlwaysTransferred ==
   [](AllLocalFileInTransferredState => []AllLocalFileInTransferredState)

DialogNeverReopensAfterAccepting ==
   []((dialog_state = "accepted") => []~(dialog_state = "open"))

(* Is everything transferred and queues empty? *)
Finished ==
   /\ AllLocalFilesAreTransferredAsInRemote
   /\ NoTransfers
   /\ LocalRemoteChannels!QuiescentChannels
   /\ LocalDialogChannels!QuiescentChannels
   /\ Remote!Quiescent
   /\ Dialog!Quiescent
   /\ UNCHANGED<<vars>>
   /\ Assert(~ForceStateTraces, "Force state trace")

Next ==
   \/ LocalNext
   \/ RemoteNext
   \/ DialogNext
   \/ Finished                  (* stutter on finish, instead of deadlock *)

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ WF_<<vars>>(Next)

(* After starting the system, at some point we end up having all files transferred *)
EventuallyAllFilesAreForeverTransferred ==
   <>[](AllLocalFilesAreTransferredAsInRemote /\ NoTransfers)

ShowsDialogToUserWhenFilesAreTransferred ==
   <>(dialog_state = "open")

(* Messages currently in the flight, for the benefit of tlsd *)
AllMessages ==
   UNION({{{<<"local", 1>>} \X {<<"remote", 1>>} \X LocalRemoteChannels!LocalToRemote!Sending}
        , {{<<"local", 1>>} \X {<<"dialog", 1>>} \X LocalDialogChannels!LocalToDialog!Sending}
        , {{<<"remote", 1>>} \X {<<"local", 1>>} \X LocalRemoteChannels!RemoteToLocal!Sending}})

(* An expression of some state, to display in the TLSD output *)
State ==
   [ local |-> <<Local!State>>,
     remote |-> <<Remote!State>>,
     dialog |-> <<Dialog!State>> ]

(* TLSD output mapping *)
AliasMessages ==
   [lane_order_json |-> ToJson(<<"dialog", "local", "remote">>),
    messages_json   |-> ToJson(AllMessages),
    state_json      |-> ToJson(State) ]

================================================================================
