---- MODULE Local --------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC
LOCAL INSTANCE FiniteSetsExt

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   local_files                  (* The files the local knows of *)
   , local_state                (* State of the scanner/transfer *)
   , local_transfers            (* On-going local_transfers *)
   , chan_local_to_remote       (* Channel from local to remote *)
   , chan_remote_to_local       (* Channel from remote to local *)

LOCAL INSTANCE Records
LOCAL INSTANCE Messages
LOCAL INSTANCE Channels

vars == <<local_files, local_state, local_transfers>>

UnchangedVars == UNCHANGED vars

----
\* Local information about the remote files
LocalFile == [remote_file : RemoteFile,
              transfer_id : {0} \cup TransferId,
              state       : {"ignore", "waiting-transfer", "transferring", "transferred"}]

\* An on-going transfer of a file
Transfer == [ remote_file : RemoteFile,
              state       : {"pending-request", "transfer", "finished", "requested-block"},
              local_size  : FileSize,
              file_id     : FileId ]

\* TypeOK invariants
LocalFileTypeOK    == local_files \in [FileId -> {<<>>} \cup LocalFile]
LocalStateTypeOK   == local_state \in {"idle", "scanning", "transferring"}
TransfersTypeOK    == local_transfers \in [TransferId -> {<<>>} \cup Transfer]

TypeOK ==
  /\ Assert(LocalFileTypeOK, <<"LocalFileTypeOK", local_files>>)
  /\ Assert(LocalStateTypeOK, <<"LocalStateTypeOK", local_state>>)
  /\ Assert(TransfersTypeOK, <<"TransfersTypeOK", local_transfers>>)

----
\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

FreeFileId == CHOOSE file_id \in FileId: local_files[file_id] = <<>>

\* Set of file names we are locally aware of
LocalFileNames == {local_files[file_id].remote_file.name: file_id \in HasFileId}

\* Are we locally aware of this file in the remote?
FoundLocally(remote_name) == \E local_file_name \in LocalFileNames: remote_name.name = local_file_name

----
(* Scanning *)

(* If scanner is idle, start scanning *)
ScanStart ==
   /\ local_state = "idle"
   /\ LocalToRemote!Send([ message |-> "list_files" ])
   /\ local_state' = "scanning"
   /\ RemoteToLocal!UnchangedVars
   /\ UNCHANGED<<local_transfers, local_files>>

ScanReceive ==
   /\ local_state = "scanning"
   /\ \E remote_file \in RemoteFile:
      /\ RemoteToLocal!Recv([ message |-> "list_files",
                              file    |-> remote_file ])
      /\ local_files' = [ local_files EXCEPT ![FreeFileId] = [
                             remote_file |-> remote_file,
                             transfer_id |-> 0,
                             state       |-> "waiting-transfer"
                          ]
                        ]
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_transfers, local_state>>

ScanFinished ==
  /\ local_state = "scanning"
  /\ local_state' = "transferring"
  /\ RemoteToLocal!Recv([ message |-> "end_list_files" ])
  /\ LocalToRemote!UnchangedVars
  /\ UNCHANGED<<local_files, local_transfers>>

(* Are there free slots in the local_transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: local_transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If the scanner has transferring, there are free transfer slots and there are files waiting transfer,
 * pick one such file and start the transfer. *)
TransferStart ==
   /\ local_state = "transferring"
   /\ \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"
   /\ \E transfer_id \in FreeTransferId:
      LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "waiting-transfer" IN
      LET local_file == local_files[file_id] IN
      /\ local_transfers' = [
            local_transfers EXCEPT ![transfer_id] = [
               remote_file |-> local_file.remote_file,
               state       |-> "pending-request",
               local_size  |-> 0,
               file_id     |-> file_id
            ]
         ]
      /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = transfer_id,
                                                                   !.state           = "transferring"]]
      /\ RemoteToLocal!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state, chans>>

(* If there are pending-request local_transfers, transfer one unit of data. If the file has already transferred
 * all the data, mark it finished.  *)
TransferRequest ==
   /\ local_state' = "transferring"
   /\ \E transfer_id \in ActiveTransferId:
         LET transfer == local_transfers[transfer_id] IN
         /\ transfer.state = "pending-request"
         /\ IF transfer.local_size < transfer.remote_file.size
            THEN /\ local_transfers' = [local_transfers EXCEPT ![transfer_id] = [@ EXCEPT !.state = "requested-block"]]
                 /\ LocalToRemote!Send([ message |-> "file_block",
                                         name    |-> transfer.remote_file.name,
                                         block   |-> transfer.local_size])
            ELSE /\ local_transfers' = [local_transfers EXCEPT ![transfer_id] = [@ EXCEPT !.state = "finished"]]
                 /\ LocalToRemote!UnchangedVars
         /\ RemoteToLocal!UnchangedVars
         /\ UNCHANGED<<local_files, local_state>>

TransferReceive ==
   /\ local_state' = "transferring"
   /\ \E transfer_id \in ActiveTransferId:
      \E block \in BlockId:
         LET transfer == local_transfers[transfer_id] IN
         /\ transfer.state = "requested-block"
         /\ RemoteToLocal!Recv([ message |-> "file_block",
                                 name    |-> transfer.remote_file.name,
                                 block   |-> block ])
         /\ local_transfers' = [local_transfers EXCEPT ![transfer_id] = [
               @ EXCEPT !.local_size = Max({block + 1, transfer.local_size}),
                        !.state      = "pending-request"
            ]]
         /\ LocalToRemote!UnchangedVars
         /\ UNCHANGED<<local_state, local_files>>

(* If the transfer is finished, release the transfer slot and mark the local file transferred *)
TransferFinished ==
   /\ local_state' = "transferring"
   /\ \E transfer_id \in ActiveTransferId:
      LET transfer == local_transfers[transfer_id] IN
      LET file_id == transfer.file_id IN
      /\ transfer.state = "finished"
      /\ local_transfers' = [local_transfers EXCEPT ![transfer_id] = <<>>]
      /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id = 0,
                                                                   !.state       = "transferred"]]
      /\ RemoteToLocal!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state>>

----
(* State *)

Next ==
  \/ ScanStart
  \/ ScanReceive
  \/ ScanFinished
  \/ TransferStart
  \/ TransferRequest
  \/ TransferReceive
  \/ TransferFinished

Init ==
  /\ local_files   = [file_id \in FileId |-> <<>>]
  /\ local_transfers     = [transfer_id \in TransferId |-> <<>>]
  /\ local_state = "idle"

(* Properties *)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================