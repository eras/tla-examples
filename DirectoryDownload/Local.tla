---- MODULE Local --------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt

CONSTANTS
   NumFiles
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
LocalStateTypeOK   == local_state \in {"idle", "running", "transferring"}
TransfersTypeOK    == local_transfers \in [TransferId -> {<<>>} \cup Transfer]

TypeOK ==
  /\ Assert(LocalFileTypeOK, <<"LocalFileTypeOK", local_files>>)
  /\ Assert(LocalStateTypeOK, <<"LocalStateTypeOK", local_state>>)
  /\ Assert(TransfersTypeOK, <<"TransfersTypeOK", local_transfers>>)

----
\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

FreeFileId == CHOOSE file_id \in FileId: local_files[file_id] = <<>>

\* Unused transfer slots are the empty tuple <<>>
FreeTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] = <<>>}
ActiveTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] # <<>>}
----
(* Scanning *)

(* If scanner is idle, start scanning *)
ScanStart(OtherUnchanged) ==
   /\ local_state = "idle"
   /\ LocalToRemote!Send([ message |-> "list_files" ])
   /\ local_state' = "running"
   /\ RemoteToLocal!UnchangedVars
   /\ UNCHANGED<<local_transfers, local_files>>
   /\ OtherUnchanged

ScanReceive(OtherUnchanged) ==
   /\ local_state = "running"
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
      /\ OtherUnchanged

ScanFinished(OtherUnchanged) ==
  /\ RemoteToLocal!Recv([ message |-> "end_list_files" ])
  /\ LocalToRemote!UnchangedVars
  /\ UNCHANGED<<local_state, local_files, local_transfers>>
  /\ OtherUnchanged

(* Are there free slots in the local_transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: local_transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If the scanner has transferring, there are free transfer slots and there are files waiting transfer,
 * pick one such file and start the transfer. *)
TransferStart(OtherUnchanged) ==
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
      /\ OtherUnchanged

(* If there are pending-request local_transfers, transfer one unit of data. If the file has already transferred
 * all the data, mark it finished.  *)
TransferRequest(OtherUnchanged) ==
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
         /\ OtherUnchanged

TransferReceive(OtherUnchanged) ==
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
         /\ OtherUnchanged

(* If the transfer is finished, release the transfer slot and mark the local file transferred *)
TransferFinished(OtherUnchanged) ==
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
      /\ OtherUnchanged

----
\* For TLSD

State ==
  [ files_ready |-> Cardinality({file_id \in FileId:
                                 /\ local_files[file_id] # <<>>
                                 /\ local_files[file_id].state = "transferred"}) ]

(* State *)

Next(OtherUnchanged) ==
  \/ ScanStart(OtherUnchanged)
  \/ ScanReceive(OtherUnchanged)
  \/ ScanFinished(OtherUnchanged)
  \/ TransferStart(OtherUnchanged)
  \/ TransferRequest(OtherUnchanged)
  \/ TransferReceive(OtherUnchanged)
  \/ TransferFinished(OtherUnchanged)

Init ==
  /\ local_files     = [file_id \in FileId |-> <<>>]
  /\ local_transfers = [transfer_id \in TransferId |-> <<>>]
  /\ local_state     = "idle"

(* Properties *)

Spec ==
  /\ Init
  /\ [][Next(TRUE)]_vars
  /\ WF_vars(Next(TRUE))

================================================================================
