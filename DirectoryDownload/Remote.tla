---- MODULE Remote -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC
LOCAL INSTANCE Sequences

CONSTANTS
   NumFiles                     (* Used by Records *)
   , NumFileNames               (* Used by Records *)
   , MaxFileSize                (* Used by Records *)
   , MaxConcurrentTransfers     (* Used by Records *)
   , MaxSendQueue               (* Maximum number of transfers we can queue *)

VARIABLES
   remote_files                 (* The files the remote has *)
   , remote_state               (* The state of the remote *)
   , remote_send_queue          (* Blocks pending send *)
   , chan_local_to_remote       (* Channel from local to remote *)
   , chan_remote_to_local       (* Channel from remote to local *)

LOCAL INSTANCE Records
LOCAL INSTANCE Messages
LOCAL INSTANCE Channels
LOCAL INSTANCE Util             (* SeqOfSet, SeqRemoveIndex *)

vars == <<remote_send_queue, remote_state, remote_files>>

UnchangedVars == UNCHANGED vars

----
\* TypeOK invariants
RemoteSendQueueOK ==
   /\ \A x \in Image(remote_send_queue): x \in MsgRemoteToLocal
   /\ Len(remote_send_queue) <= MaxSendQueue

RemoteStateOK ==
   remote_state \in [ listing_files: BOOLEAN,
                      listed_file_index: {0} \cup FileId ]

RemoteFileTypeOK     ==
   /\ \A remote_file \in Image(remote_files): remote_file \in RemoteFile
   /\ ~\E remote_file1 \in Image(remote_files):
      \E remote_file2 \in Image(remote_files):
      /\ remote_file1.name = remote_file2.name
      /\ remote_file1.size # remote_file2.size

TypeOK ==
   /\ Assert(RemoteSendQueueOK, <<"RemoteSendQueueOK", remote_send_queue>>)
   /\ Assert(RemoteStateOK, <<"RemoteStateOK", remote_state>>)
   /\ Assert(RemoteFileTypeOK, <<"RemoteFileTypeOK", remote_files>>)

----
\* Generate uniquely named file of different names and varying sizes
RECURSIVE GenerateFiles(_)
GenerateFiles(files) ==
  IF \E file \in RemoteFile: file.name \notin {file2.name: file2 \in files}
  THEN LET file == CHOOSE file \in RemoteFile:
                   /\ file.name \notin {file2.name: file2 \in files}
                   /\ \lnot \E file2 \in files: file.size <= file2.size
       IN GenerateFiles({file} \union files)
  ELSE files

----
(* Scanning *)

(* If scanner is idle, start scanning *)
HandleListFilesStart ==
  /\ \lnot remote_state.listing_files
  /\ LocalToRemote!Recv([ message |-> "list_files" ])
  /\ remote_state' = [remote_state EXCEPT !.listing_files = TRUE
                                        , !.listed_file_index = 0]
  /\ UNCHANGED<<remote_send_queue, remote_files, chan_remote_to_local>>

EnqueueSend(message) ==
  /\ Len(remote_send_queue) < MaxSendQueue
  /\ remote_send_queue' = remote_send_queue \o <<message>>

HandleListFilesDo ==
  /\ remote_state.listing_files
  /\ IF remote_state.listed_file_index < Len(remote_files)
     THEN
        LET remote_file == remote_files[remote_state.listed_file_index + 1] IN
        /\ EnqueueSend([ message |-> "list_files",
                         file    |-> remote_file ])
        /\ remote_state' = [remote_state EXCEPT !.listed_file_index = @ + 1]
     ELSE
        /\ EnqueueSend([ message |-> "end_list_files" ])
        /\ remote_state' = [remote_state EXCEPT !.listing_files = FALSE
                                              , !.listed_file_index = 0]
  /\ UNCHANGED<<chan_remote_to_local, chan_local_to_remote, remote_files>>

HandleBlockRequest ==
   \E block \in BlockId:
   \E name \in FileName:
      /\ LocalToRemote!Recv([ message |-> "file_block",
                              name    |-> name,
                              block   |-> block ])
      /\ EnqueueSend([ message |-> "file_block",
                       name    |-> name,
                       block   |-> block ])
      /\ UNCHANGED<<chan_remote_to_local, remote_files, remote_state>>

HandleSendQueue ==
   /\ Len(remote_send_queue) > 0
   /\ \E index \in DOMAIN remote_send_queue:
      /\ RemoteToLocal!Send(remote_send_queue[index])
      /\ remote_send_queue' = SeqRemoveIndex(remote_send_queue, index)
      /\ UNCHANGED<<chan_local_to_remote, remote_files, remote_state>>

Next ==
  \/ HandleListFilesStart
  \/ HandleListFilesDo
  \/ HandleBlockRequest
  \/ HandleSendQueue

Quiescent == ~ENABLED(Next)

Init ==
  /\ remote_files = SeqOfSet(GenerateFiles({}))
  /\ remote_state = [ listing_files     |-> FALSE,
                      listed_file_index |-> 0 ]
  /\ remote_send_queue = <<>>

================================================================================
