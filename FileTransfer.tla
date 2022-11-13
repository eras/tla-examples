---- MODULE FileTransfer -------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC

CONSTANTS
   NumFiles
   , NumFileNames
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   peer_files
   , local_files
   , scanner_state
   , transfers

vars == <<peer_files, local_files, scanner_state, transfers>>

FileId == (1..NumFiles)

TransferId == (1..MaxConcurrentTransfers)
FreeTransferId == {transfer_id \in TransferId: transfers[transfer_id] = <<>>}
ActiveTransferId == {transfer_id \in TransferId: transfers[transfer_id] # <<>>}

FileName == {"filename"} \X (1..NumFileNames)
FileSize == (0..MaxFileSize)

PeerFile == [name: FileName,
             size: FileSize]

LocalFile == {<<>>} \cup [peer_file   : PeerFile,
                          transfer_id : {0} \cup TransferId,
                          state       : {"ignore", "pending", "transferring", "transferred"}]

Transfer == {<<>>} \cup [peer_file  : PeerFile,
                         state      : {"active", "transfer", "finished"},
                         local_size : FileSize,
                         file_id    : FileId]

PeerFileTypeOK     == \A peer_file \in peer_files: peer_file \in PeerFile
LocalFileTypeOK    == local_files \in [FileId -> LocalFile]
ScannerStateTypeOK == scanner_state \in {"idle", "scanning", "scanned"}
TransfersTypeOK    == transfers \in [TransferId -> Transfer]

RECURSIVE GenerateFiles(_)
GenerateFiles(files) ==
  IF \E file \in PeerFile: file.name \notin {file2.name: file2 \in files}
  THEN LET file == CHOOSE file \in PeerFile:
                   /\ file.name \notin {file2.name: file2 \in files}
                   /\ \lnot \E file2 \in files: file.size <= file2.size
       IN GenerateFiles({file} \union files)
  ELSE files

HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

LocalFileNames == {local_files[file_id].peer_file.name: file_id \in HasFileId}

NotFoundLocally(peer_file) == \lnot \E local_file_name \in LocalFileNames: peer_file.name = local_file_name

(* Scanning *)

ScanStart ==
  /\ scanner_state = "idle"
  /\ scanner_state' = "scanning"
  /\ UNCHANGED<<transfers, peer_files, local_files>>

ScanDo ==
  /\ scanner_state = "scanning"
  /\ IF \E peer_file \in peer_files: NotFoundLocally(peer_file) THEN
        LET peer_file == CHOOSE peer_file \in peer_files: NotFoundLocally(peer_file) IN
        LET file_id == CHOOSE file_id \in FileId: local_files[file_id] = <<>> IN
        /\ local_files' = [local_files EXCEPT ![file_id] = [peer_file |-> peer_file,
                                                            transfer_id |-> 0,
                                                            state |-> "pending"]]
        /\ UNCHANGED<<transfers, peer_files, scanner_state>>
     ELSE
        /\ scanner_state' = "scanned"
        /\ UNCHANGED<<transfers, peer_files, local_files>>

(* Transfer *)

HasFreeTransferSlot == \E transfer_id \in TransferId: transfers[transfer_id] = <<>>

HasFilePendingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "pending"

TransferStart ==
  /\ scanner_state = "scanned"
  /\ HasFreeTransferSlot /\ HasFilePendingTransfer
  /\ \E file_id \in HasFileId: local_files[file_id].state = "pending"
  /\ \E transfer_id \in FreeTransferId:
     LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "pending" IN
     LET local_file == local_files[file_id] IN
     /\ transfers' = [transfers EXCEPT ![transfer_id] = [peer_file  |-> local_file.peer_file,
                                                         state      |-> "active",
                                                         local_size |-> 0,
                                                         file_id    |-> file_id]]
     /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = transfer_id,
                                                                  !.state           = "transferring"]]
     /\ UNCHANGED<<peer_files, scanner_state>>

TransferDo ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  /\ transfer.state = "active"
  /\ IF transfer.local_size < transfer.peer_file.size
     THEN transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.local_size = transfer.local_size + 1]]
     ELSE transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.state = "finished"]]
  /\ UNCHANGED<<peer_files, local_files, scanner_state>>

TransferFinished ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  LET file_id == transfer.file_id IN
  /\ transfer.state = "finished"
  /\ transfers' = [transfers EXCEPT ![transfer_id] = <<>>]
  /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = 0,
                                                               !.state           = "transferred"]]
  /\ UNCHANGED<<peer_files, scanner_state>>

(* State *)

Stutter == UNCHANGED<<vars>>

Next ==
  \/ ScanStart
  \/ ScanDo
  \/ TransferStart
  \/ TransferDo
  \/ TransferFinished
  \/ Stutter

Init ==
  /\ peer_files    = GenerateFiles({})
  /\ local_files   = [file_id \in FileId |-> <<>>]
  /\ transfers     = [transfer_id \in TransferId |-> <<>>]
  /\ scanner_state = "idle"

(* Properties *)

EventuallyAllFilesAreTransferred ==
  Init =>
  <>\A peer_file \in peer_files:
    \E file_id \in HasFileId:
    /\ local_files[file_id].peer_file = peer_file
    /\ local_files[file_id].state = "transferred"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================
