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

(* Used from Main to express this module does not modify variables *)
UnchangedVars == UNCHANGED vars

----
\* Local information about the remote files
LocalFile == [remote_file : RemoteFile,
              transfer_id : {0} \cup TransferId,
              state       : {"waiting-transfer", (* waiting to be transferred *)
                             "transferring",     (* transferring *)
                             "transferred"}]     (* transferred *)

\* An on-going transfer of a file
Transfer == [ remote_file : RemoteFile,         (* information about the file we're transferring *)
              state       : {"transferring",    (* waiting to be requested from remote *)
                             "finished"},       (* transfer is complete *)
              request_next: FileSize,           (* current size of the local file *)
              blocks_received : FileSize,       (* the number of received blocks *)
              file_id     : FileId ]

\* TypeOK invariants
LocalFilesTypeOK     == local_files \in [FileId -> {<<>>} \cup LocalFile]
LocalStateTypeOK     == local_state \in {"idle", "running", "transferring"}
LocalTransfersTypeOK == local_transfers \in [TransferId -> {<<>>} \cup Transfer]

(* Assert is used to more easily determine which of the TypeOK constraints failed *)
TypeOK ==
  /\ Assert(LocalFilesTypeOK, <<"LocalFilesTypeOK", local_files>>)
  /\ Assert(LocalStateTypeOK, <<"LocalStateTypeOK", local_state>>)
  /\ Assert(LocalTransfersTypeOK, <<"LocalTransfersTypeOK", local_transfers>>)

----
\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

\* Get an index for an empty entry in local_files
FreeFileId == CHOOSE file_id \in FileId: local_files[file_id] = <<>>

\* Unused transfer slots are the empty tuple <<>>; get the set of unused transfer ids
FreeTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] = <<>>}

\* Get the set of active transfer ids
ActiveTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] # <<>>}
----
(* Scanning *)

(* If scanner is idle, start running and send the list_files request to remote *)
ScanStart(OtherUnchanged) ==
   /\ local_state = "idle"
   /\ LocalToRemote!Send([ message |-> "list_files" ])
   /\ local_state' = "running"
   /\ RemoteToLocal!UnchangedVars
   /\ UNCHANGED<<local_transfers, local_files>>
   /\ OtherUnchanged

(* Receive and process list_files-responses from the remote *)
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

(* Receive and process end_list_files-response from the remote *)
ScanFinished(OtherUnchanged) ==
  /\ RemoteToLocal!Recv([ message |-> "end_list_files" ])
  /\ LocalToRemote!UnchangedVars
  /\ UNCHANGED<<local_state, local_files, local_transfers>>
  /\ OtherUnchanged

(* Are there free slots in the local_transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: local_transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If there are local files waiting to be transferred and we have space in the transfer queue,
 * start transferring one such file by adding a new entry to local_transfers *)
TransferStart(OtherUnchanged) ==
   /\ \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"
   /\ \E transfer_id \in FreeTransferId:
      LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "waiting-transfer" IN
      LET local_file == local_files[file_id] IN
      /\ local_transfers' = [
            local_transfers EXCEPT ![transfer_id] = [
               remote_file  |-> local_file.remote_file,
               state        |-> "transferring",
               request_next |-> 0,
               blocks_received |-> 0,
               file_id      |-> file_id
            ]
         ]
      /\ local_files' = [local_files EXCEPT ![file_id].transfer_id = transfer_id,
                                            ![file_id].state       = "transferring"]
      /\ RemoteToLocal!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state, chans>>
      /\ OtherUnchanged

(* If there are pending-request local_transfers and the file is not completely transferred,
 * request one unit of data. If the file is completely transferred, mark the transfer finished. *)
TransferRequest(OtherUnchanged) ==
   /\ \E transfer_id \in ActiveTransferId:
         LET transfer == local_transfers[transfer_id] IN
         /\ transfer.state = "transferring"
         /\ transfer.request_next < transfer.remote_file.size
         /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].request_next = @ + 1]
         /\ LocalToRemote!Send([ message |-> "file_block",
                                 name    |-> transfer.remote_file.name,
                                 block   |-> transfer.request_next ])
         /\ RemoteToLocal!UnchangedVars
         /\ UNCHANGED<<local_files, local_state>>
         /\ OtherUnchanged

(* Receive a block of data from the remote *)
TransferReceive(OtherUnchanged) ==
   /\ \E transfer_id \in ActiveTransferId:
      \E block \in BlockId:
         LET transfer == local_transfers[transfer_id] IN
         /\ transfer.state = "transferring"
         /\ IF transfer.blocks_received = transfer.remote_file.size
            THEN /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].state = "finished"]
                 /\ RemoteToLocal!UnchangedVars
            ELSE /\ RemoteToLocal!Recv([ message |-> "file_block",
                                         name    |-> transfer.remote_file.name,
                                         block   |-> block ])
                 /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].blocks_received = @ + 1]
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
      /\ local_files' = [local_files EXCEPT ![file_id].transfer_id = 0,
                                            ![file_id].state       = "transferred"]
      /\ RemoteToLocal!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state>>
      /\ OtherUnchanged

----
\* State description for TLSD
State ==
  [ files_ready |-> Cardinality({file_id \in FileId:
                                 /\ local_files[file_id] # <<>>
                                 /\ local_files[file_id].state = "transferred"}) ]

(* State *)

Next(OtherUnchanged) ==
   \/ ScanStart(OtherUnchanged)                  (* Start scannning *)
   \/ ScanReceive(OtherUnchanged)                (* Receive scan results *)
   \/ ScanFinished(OtherUnchanged)               (* Finish scanning *)
   \/ TransferStart(OtherUnchanged)              (* Start transfer of one file; acquire transfer slot *)
   \/ TransferRequest(OtherUnchanged)            (* Request a block for one file *)
   \/ TransferReceive(OtherUnchanged)            (* Receive a block for one file *)
   \/ TransferFinished(OtherUnchanged)           (* Clean up a transfer; release transfer slot *)

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
